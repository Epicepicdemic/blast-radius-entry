"""Link pin-only call observations to exact boolean keyword tokens in the pinned source."""
import ast


def equivalent(consumer, origin, kind):
    if consumer not in ("parse", "forward-to-parse", "identifier", "clone"):
        return False
    # When the operand is an exact string, neither parser nor identifier builder
    # examines the flag. A detached tree has no externally visible input identity.
    if kind == "str" and origin == "scalar":
        return consumer != "clone"
    if origin not in {"owned:table_", "owned:to_identifier", "owned:Identifier",
                      "owned:TableAlias", "owned:Table"}:
        return False
    if consumer == "identifier":
        return kind == "Identifier"
    return kind in {"Table", "TableAlias", "Identifier"}


def link(pin, files, profile, ids, masks):
    if (profile["ids"] != ids or profile["exitstatus"] or profile["passed"] != len(ids)
            or profile["tasks"] != profile["joined"] or int(profile["incomplete"], 16)):
        raise ValueError("incomplete ownership observation")
    by_path = {}
    for site, observations in profile["domains"].items():
        path, line, column = site.rsplit(":", 2)
        by_path.setdefault(path, {})[int(line), int(column)] = observations
    for path, sites in by_path.items():
        section = files.get(path)
        if section is None:
            continue
        tree = ast.parse((pin / path).read_bytes())
        parents = {child: parent for parent in ast.walk(tree) for child in ast.iter_child_nodes(parent)}
        for node in ast.walk(tree):
            if not isinstance(node, ast.Call):
                continue
            facts = sites.get((node.lineno, node.col_offset))
            if not facts or any(not equivalent(c, o, k) for c, o, k, _ in facts):
                continue
            values = [kw.value for kw in node.keywords if kw.arg == "copy"]
            if len(values) != 1 or not isinstance(values[0], ast.Constant) or type(values[0].value) is not bool:
                continue
            value = values[0]
            observed = 0
            for *_, bits in facts:
                observed |= int(bits, 16)
            reached = 0
            for line in range(node.lineno, node.end_lineno + 1):
                for key in ("cold_lines", "lines"):
                    idx = section[key].get(line)
                    if idx is not None:
                        reached |= masks[idx]
            if not reached or reached & ~observed:
                continue
            # Include exactly one unambiguous named scope and exclude nested closures
            # whose code object could be observed independently of the outer function.
            owners = [name for name, (_, start, end, _) in section["functions"].items()
                      if start <= node.lineno <= node.end_lineno <= end]
            scopes = []
            parent = parents.get(node)
            while parent is not None:
                if isinstance(parent, (ast.Lambda, ast.FunctionDef, ast.AsyncFunctionDef)):
                    scopes.append(parent)
                parent = parents.get(parent)
            if len(owners) == 1 and len(scopes) == 1 and not isinstance(scopes[0], ast.Lambda):
                section.setdefault("owned_copy", {}).setdefault(value.lineno, []).append(
                    (value.col_offset, value.value, owners[0]))


def unchanged_copy(section, change, left, right):
    if len(change.removed) != 1 or change.removed != change.added or change.insertions:
        return None
    line = next(iter(change.removed))
    for col, original, scope in section.get("owned_copy", {}).get(line, ()):
        old, new = (b"True", b"False") if original else (b"False", b"True")
        before = left[line - 1].encode()
        if before[col:col + len(old)] == old and right[line - 1].encode() == before[:col] + new + before[col + len(old):]:
            return scope
    return None
