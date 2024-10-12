local overseer = require("overseer")
local actions = require "telescope.actions"
local sorters = require "telescope.sorters"
local action_state = require "telescope.actions.state"
local finders = require "telescope.finders"
local make_entry = require "telescope.make_entry"
local pickers = require "telescope.pickers"
local utils = require "telescope.utils"

local conf = require("telescope.config").values

local dk_files = {}
local lean_files = {}
vim.list_extend(dk_files, vim.split(vim.fn.glob("dk/**/*.dk"), "\n"))
vim.list_extend(lean_files, vim.split(vim.fn.glob("*.lean"), "\n"))
vim.list_extend(lean_files, vim.split(vim.fn.glob("Lean4Less/**/*.lean"), "\n"))
vim.list_extend(lean_files, vim.split(vim.fn.glob("patch/**/*.lean"), "\n"))

local prev_mod_file = vim.fn.stdpath("data") .. "/" .. "l4l_prev_trans.json"
local prev_mod = vim.fn.filereadable(prev_mod_file) ~= 0 and vim.fn.json_decode(vim.fn.readfile(prev_mod_file)) or {}
local curr_module

-- choose the most recently translated file
local max_ts = 0
for prev, time in pairs(prev_mod) do
  if time > max_ts then
    curr_module = prev
    max_ts = time
  end
end

local templates = {
  ["translate"] = {
    builder = function(params)
      return {
        cmd = { "lake" },
        args = { "exe", "lean4less", params.mod},
        components = {
          -- { "restart_on_save", paths = lean_files}, -- TODO "intelligently" switch task to check if a dk file was modified
          "default",
        },
      }
    end,
  },
  ["translate only"] = {
    builder = function(params)
      return {
        cmd = { "lake" },
        args = { "exe", "lean4less", params.mod, "--only", params.only},
        components = {
          -- { "restart_on_save", paths = lean_files},
          "default",
        },
      }
    end,
  },
}

local function region_to_text()
  local _, ls, cs = unpack(vim.fn.getpos('v'))
  local _, le, ce = unpack(vim.fn.getpos('.'))
  local swap = ls > le or (ls == le and cs > ce)
  ls, cs, le, ce = unpack(swap and {le, ce, ls, cs} or {ls, cs, le, ce})
  local text = vim.api.nvim_buf_get_text(0, ls-1, cs-1, le-1, ce, {})[1]
  return text
end

local curr_task, curr_task_win

local abort_curr_task = function ()
  if curr_task then
    if vim.api.nvim_win_is_valid(curr_task_win) then
      vim.api.nvim_win_close(curr_task_win, true)
    end
    overseer.run_action(curr_task, "unwatch")
    curr_task:stop()
    curr_task:dispose()
  end
end

local function task_split (task)
  abort_curr_task()

  local main_win = vim.api.nvim_get_current_win()
  overseer.run_action(task, "open vsplit")
  curr_task_win = vim.api.nvim_get_current_win()
  vim.cmd("wincmd L")
  vim.cmd("wincmd 170|")
  vim.cmd("set winfixwidth")
  vim.cmd("set wrap")

  vim.api.nvim_set_current_win(main_win)
  curr_task = task
end


local prev_onlys_file = vim.fn.stdpath("data") .. "/" .. "l4l_prev_onlys.json"
local prev_onlys = vim.fn.filereadable(prev_onlys_file) ~= 0 and vim.fn.json_decode(vim.fn.readfile(prev_onlys_file)) or {}
for only, only_info in pairs(prev_onlys) do
  if type(only_info) == "number" then
    prev_onlys[only] = nil
  end
end
local json = vim.fn.json_encode(prev_onlys)
vim.fn.writefile({json}, prev_onlys_file)

local last_template
local last_params = {}

local function run_template(name, params)
  last_template = name
  last_params = params or {}
  overseer.run_template({name = name, params = params}, task_split)
end

local function resume_prev_template()
  if not last_template then print("no previous template run, aborting...") return end
  run_template(last_template, last_params)
end

local function choose_mod(mod)
  prev_mod[mod] = os.time()
  local json = vim.fn.json_encode(prev_mod)
  vim.fn.writefile({json}, prev_mod_file)
  curr_module = mod
end

local function _run_only(only_info)
  only_info.time = os.time()

  local json = vim.fn.json_encode(prev_onlys)
  vim.fn.writefile({json}, prev_onlys_file)

  choose_mod(only_info.mod)
  run_template("translate only", {only = only_info.const, mod = only_info.mod})
end

local function run_only(const, mod)
  mod = mod or curr_module
  if #const == 0 then print"Error: no constant specified" return end
  local key = mod .. "->" .. const
  local only_info = prev_onlys[key] or {const = const, mod = mod}
  prev_onlys[key] = only_info
  _run_only(only_info)
end

local transmod_picker = function(opts)
  opts = opts or {}

  local results = {}

  for module, _ in pairs(prev_mod) do
    if module ~= curr_module then
      table.insert(results, module)
    end
  end

  return pickers
    .new(opts, {
      prompt_title = string.format("Choose module to translate (current: %s)", vim.fn.fnamemodify(curr_module, ":t")),
      finder = finders.new_table {
        results = results,
        entry_maker = opts.entry_maker or make_entry.gen_from_file(opts),
      },
      sorter = sorters.Sorter:new {
        discard = true,

        scoring_function = function(_, _, line)
          return prev_mod[line] and -prev_mod[line] or 0
        end,
      },
      previewer = conf.grep_previewer(opts),
      attach_mappings = function(prompt_bufnr)
        actions.select_default:replace(function()
          local selection = action_state.get_selected_entry()

          actions.close(prompt_bufnr)
          choose_mod(selection.value)
          if last_template == "translate" or last_template == "translate only" then
            run_template(last_template, vim.tbl_extend("keep", {mod = curr_module}, last_params))
          end
        end)

        return true
      end,
    })
end

local only_picker = function(opts) return pickers
  .new(opts, {
    prompt_title = "previous --only args",
    finder = finders.new_table {
      results = (function()
        local onlys = {}
        for key, only_info in pairs(prev_onlys) do
          local mod = type(only_info) == "table" and only_info.mod
          local info = {const = key, text = mod .. " --> " .. only_info.const}
          table.insert(onlys, info)
        end
        return onlys
      end)(),

      entry_maker = function(entry)
        return make_entry.set_default_entry_mt({
          value = entry.const,
          ordinal = entry.const,
          display = entry.text,
        })
      end
    },
    sorter = sorters.Sorter:new {
      discard = true,

      scoring_function = function(_, _, entry)
        if type(prev_onlys[entry]) == "number" then
          return -prev_onlys[entry]
        end
        return -prev_onlys[entry].time
      end,
    },
    attach_mappings = function(prompt_bufnr, map)
      actions.select_default:replace(function()
        local selection = action_state.get_selected_entry()
        if selection == nil then
          utils.__warn_no_selection "--only args"
          return
        end

        actions.close(prompt_bufnr)
        local val = selection.value

        _run_only(prev_onlys[val])
      end)
      map("n", "yy", function()
        local selection = action_state.get_selected_entry()
        local only = prev_onlys[selection.value]
        vim.fn.setreg('"', only.const)
        print('yanked: ' .. vim.inspect(only.const))
      end)

      return true
    end,
  })
end

for name, template in pairs(templates) do
  template.name = name
  overseer.register_template(template)
end

vim.keymap.set("n", "<leader>tt", function () run_template("translate", {mod = curr_module}) end)
vim.keymap.set("n", "<leader>to", function () run_only(vim.fn.input("enter constant names (comma-separated, no whitespace): ")) end)
vim.keymap.set("n", "<leader>tF", function () choose_mod(vim.fn.input("enter module name: ")) end)
vim.keymap.set("v", "<leader>to", function () run_only(region_to_text()) end)
vim.keymap.set("n", "<leader>tO", function () only_picker():find() end)
vim.keymap.set("n", "<leader>tf", function () transmod_picker():find() end)
vim.keymap.set("n", "<leader>tq", function () abort_curr_task() end)
vim.keymap.set("n", "<leader>t<Tab>", function () resume_prev_template() end)
