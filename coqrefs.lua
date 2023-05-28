local coqdir = "."
local texdir = "../../lir"

local texfiles = texdir .. "/*.tex"
local resultfile = "index.md"
local auxfile = texdir .. "/main.aux"


local Refs = {}
do
  local f = assert(io.open(auxfile))
  for line in f:lines() do
    local def, ref = string.match(line, "^\\newlabel(%b{}){{(%w+)}")
    if def then
      def = string.sub(def, 2, -2)
      Refs[def] = ref
    end
  end
end

local f = assert(io.popen("grep Coqlabel " .. texfiles))

local t = f:read("*a")

f:close()

f = assert(io.open(resultfile, "w"))

f:write[[
# Index to the Coq Definitions

Follows an index of all Coq definitions (including inductive types,
lemmas, theorems, etc.) used in the text:

]]

local kind = {l = "Lemma", t = "Theorem", f = "Figure"}

for ref, file, def, t in
      string.gmatch(t, "\\Coqlabel(%b{})(%b{})(%b{})(%b{})") do

  local ref = string.sub(ref, 2, -2)
  local file = string.sub(file, 2, -2)
  local def = string.sub(def, 2, -2)
  local t = kind[string.sub(t, 2, -2)]

  local what

  do
    local f = assert(io.open(coqdir .. "/" .. file))
    local t = f:read("*a")
    f:close()
    what = {}
    for def in string.gmatch(def, "(%w+)") do
      local code = string.match(t, "\n(%u%w+) " .. def .. "%W")
      if code then
        what[#what + 1] = string.format("%s `%s`", code, def)
      else
        print("-------- Undef -----", file, def)
      end
    end
    what = table.concat(what, ", ")
  end

  if not Refs[ref] then print("undefined ", ref) end

  f:write(string.format("- %s %s: %s in file `%s`\n",
                        t, Refs[ref], what, file))
end

assert(f:close())

