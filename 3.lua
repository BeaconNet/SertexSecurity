local args = {...}

-- SHA256
local MOD = 2^32
local MODM = MOD-1
 
local function memoize(f)
        local mt = {}
        local t = setmetatable({}, mt)
        function mt:__index(k)
                local v = f(k)
                t[k] = v
                return v
        end
        return t
end
 
local function make_bitop_uncached(t, m)
        local function bitop(a, b)
                local res,p = 0,1
                while a ~= 0 and b ~= 0 do
                        local am, bm = a % m, b % m
                        res = res + t[am][bm] * p
                        a = (a - am) / m
                        b = (b - bm) / m
                        p = p*m
                end
                res = res + (a + b) * p
                return res
        end
        return bitop
end
 
local function make_bitop(t)
        local op1 = make_bitop_uncached(t,2^1)
        local op2 = memoize(function(a) return memoize(function(b) return op1(a, b) end) end)
        return make_bitop_uncached(op2, 2 ^ (t.n or 1))
end
 
local bxor1 = make_bitop({[0] = {[0] = 0,[1] = 1}, [1] = {[0] = 1, [1] = 0}, n = 4})
 
local function bxor(a, b, c, ...)
        local z = nil
        if b then
                a = a % MOD
                b = b % MOD
                z = bxor1(a, b)
                if c then z = bxor(z, c, ...) end
                return z
        elseif a then return a % MOD
        else return 0 end
end
 
local function band(a, b, c, ...)
        local z
        if b then
                a = a % MOD
                b = b % MOD
                z = ((a + b) - bxor1(a,b)) / 2
                if c then z = bit32_band(z, c, ...) end
                return z
        elseif a then return a % MOD
        else return MODM end
end
 
local function bnot(x) return (-1 - x) % MOD end
 
local function rshift1(a, disp)
        if disp < 0 then return lshift(a,-disp) end
        return math.floor(a % 2 ^ 32 / 2 ^ disp)
end
 
local function rshift(x, disp)
        if disp > 31 or disp < -31 then return 0 end
        return rshift1(x % MOD, disp)
end
 
local function lshift(a, disp)
        if disp < 0 then return rshift(a,-disp) end
        return (a * 2 ^ disp) % 2 ^ 32
end
 
local function rrotate(x, disp)
    x = x % MOD
    disp = disp % 32
    local low = band(x, 2 ^ disp - 1)
    return rshift(x, disp) + lshift(low, 32 - disp)
end
 
local k = {
        0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5,
        0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
        0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3,
        0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
        0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc,
        0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
        0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
        0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
        0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
        0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
        0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3,
        0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
        0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5,
        0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
        0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
        0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
}
 
local function str2hexa(s)
        return (string.gsub(s, ".", function(c) return string.format("%02x", string.byte(c)) end))
end
 
local function num2s(l, n)
        local s = ""
        for i = 1, n do
                local rem = l % 256
                s = string.char(rem) .. s
                l = (l - rem) / 256
        end
        return s
end
 
local function s232num(s, i)
        local n = 0
        for i = i, i + 3 do n = n*256 + string.byte(s, i) end
        return n
end
 
local function preproc(msg, len)
        local extra = 64 - ((len + 9) % 64)
        len = num2s(8 * len, 8)
        msg = msg .. "\128" .. string.rep("\0", extra) .. len
        assert(#msg % 64 == 0)
        return msg
end
 
local function initH256(H)
        H[1] = 0x6a09e667
        H[2] = 0xbb67ae85
        H[3] = 0x3c6ef372
        H[4] = 0xa54ff53a
        H[5] = 0x510e527f
        H[6] = 0x9b05688c
        H[7] = 0x1f83d9ab
        H[8] = 0x5be0cd19
        return H
end
 
local function digestblock(msg, i, H)
        local w = {}
        for j = 1, 16 do w[j] = s232num(msg, i + (j - 1)*4) end
        for j = 17, 64 do
                local v = w[j - 15]
                local s0 = bxor(rrotate(v, 7), rrotate(v, 18), rshift(v, 3))
                v = w[j - 2]
                w[j] = w[j - 16] + s0 + w[j - 7] + bxor(rrotate(v, 17), rrotate(v, 19), rshift(v, 10))
        end
 
        local a, b, c, d, e, f, g, h = H[1], H[2], H[3], H[4], H[5], H[6], H[7], H[8]
        for i = 1, 64 do
                local s0 = bxor(rrotate(a, 2), rrotate(a, 13), rrotate(a, 22))
                local maj = bxor(band(a, b), band(a, c), band(b, c))
                local t2 = s0 + maj
                local s1 = bxor(rrotate(e, 6), rrotate(e, 11), rrotate(e, 25))
                local ch = bxor (band(e, f), band(bnot(e), g))
                local t1 = h + s1 + ch + k[i] + w[i]
                h, g, f, e, d, c, b, a = g, f, e, d + t1, c, b, a, t1 + t2
        end
 
        H[1] = band(H[1] + a)
        H[2] = band(H[2] + b)
        H[3] = band(H[3] + c)
        H[4] = band(H[4] + d)
        H[5] = band(H[5] + e)
        H[6] = band(H[6] + f)
        H[7] = band(H[7] + g)
        H[8] = band(H[8] + h)
end
 
local function sha256(msg)
        msg = preproc(msg, string.len(msg))
        local H = initH256({})
        for i = 1, #msg, 64 do digestblock(msg, i, H) end
        return str2hexa(num2s(H[1], 4) .. num2s(H[2], 4) .. num2s(H[3], 4) .. num2s(H[4], 4) ..
                num2s(H[5], 4) .. num2s(H[6], 4) .. num2s(H[7], 4) .. num2s(H[8], 4))
end

-- DB

--[[

	Database API Created by Ale32bit
	
	db v2.2
	
	MIT License

	Copyright (c) 2017 Ale32bit

	Permission is hereby granted, free of charge, to any person obtaining a copy
	of this software and associated documentation files (the "Software"), to deal
	in the Software without restriction, including without limitation the rights
	to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
	copies of the Software, and to permit persons to whom the Software is
	furnished to do so, subject to the following conditions:

	The above copyright notice and this permission notice shall be included in all
	copies or substantial portions of the Software.

	THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
	IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
	FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
	AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
	LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
	OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
	SOFTWARE.

]]--

local database = "/.sertexsecurity" -- Config file

local db = {}

if fs.isDir(database) then
	error("database must be a file")
end

if not fs.exists(database) then
	local data = {
		database = {
			version = 2.2,
		}
	}
	local f = fs.open(database,"w")
	f.write(textutils.serialise(data))
	f.close()
end

-- init

local f = fs.open(database,"r")
db = textutils.unserialise(f.readAll())
f.close()
if not db then
	db = {
		database = {
			version = 2.2,
		}
	}
end

local function checkDatabase()
  local f = fs.open(database,"r")
  local data = textutils.unserialise(f.readAll())
  f.close()
  if data then
    return true
  end
  return false
end

local function get(group,config)
	if not db[group] then
		return nil
	end
	if not config then
		return db[group]
	end
	return db[group][config]
end

local function set(group,config,value)
	local old = db
	if not db[group] then
		db[group] = {}
	end
	db[group][config] = value
	if not db then
		db = old
		return false
	end
	local f = fs.open(database,"w")
	f.write(textutils.serialise(db))
	f.close()
	return true
end

local function list(group)
	return db[group]
end

local function index()
	return db
end

local function update() --update from file
	if not checkDatabase() then
		return false, "database corrupted"
	end
	local f = fs.open(database,"r")
	db = textutils.unserialise(f.readAll())
	f.close()
	return true
end

local function fixFile() --update file from memory
	local f = fs.open(database, "w")
	f.write(textutils.serialize(db))
	f.close()
end

local function delete(group)
	db[group] = nil
	local f = fs.open(database,"w")
	f.write(textutils.serialise(db))
	f.close()
end

-- END APIs

local function read( _sReplaceChar, _tHistory, _fnComplete, _MouseEvent, _presetInput )
    term.setCursorBlink( true )
    local sLine = _presetInput
		
		if type(sLine) ~= "string" then
			sLine = ""
		end
		local nPos = #sLine
    local nHistoryPos
		local _MouseX
		local _MouseY
		local param
		local sEvent
		local usedMouse = false
    if _sReplaceChar then
        _sReplaceChar = string.sub( _sReplaceChar, 1, 1 )
    end

    local tCompletions
    local nCompletion
    local function recomplete()
        if _fnComplete and nPos == string.len(sLine) then
            tCompletions = _fnComplete( sLine )
            if tCompletions and #tCompletions > 0 then
                nCompletion = 1
            else
                nCompletion = nil
            end
        else
            tCompletions = nil
            nCompletion = nil
        end
    end

    local function uncomplete()
        tCompletions = nil
        nCompletion = nil
    end

    local w = term.getSize()
    local sx = term.getCursorPos()

    local function redraw( _bClear )
        local nScroll = 0
        if sx + nPos >= w then
            nScroll = (sx + nPos) - w
        end

        local cx,cy = term.getCursorPos()
        term.setCursorPos( sx, cy )
        local sReplace = (_bClear and " ") or _sReplaceChar
        if sReplace then
            term.write( string.rep( sReplace, math.max( string.len(sLine) - nScroll, 0 ) ) )
        else
            term.write( string.sub( sLine, nScroll + 1 ) )
        end

        if nCompletion then
            local sCompletion = tCompletions[ nCompletion ]
            local oldText, oldBg
            if not _bClear then
                oldText = term.getTextColor()
                oldBg = term.getBackgroundColor()
                term.setTextColor( colors.gray )
            end
            if sReplace then
                term.write( string.rep( sReplace, string.len( sCompletion ) ) )
            else
                term.write( sCompletion )
            end
            if not _bClear then
                term.setTextColor( oldText )
                term.setBackgroundColor( oldBg )
            end
        end

        term.setCursorPos( sx + nPos - nScroll, cy )
    end
    
    local function clear()
        redraw( true )
    end

    recomplete()
    redraw()

    local function acceptCompletion()
        if nCompletion then
            -- Clear
            clear()

            -- Find the common prefix of all the other suggestions which start with the same letter as the current one
            local sCompletion = tCompletions[ nCompletion ]
            sLine = sLine .. sCompletion
            nPos = string.len( sLine )

            -- Redraw
            recomplete()
            redraw()
        end
    end
    while true do
        sEvent, param,_MouseX,_MouseY = os.pullEvent()
        if sEvent == "char" then
            -- Typed key
            clear()
            sLine = string.sub( sLine, 1, nPos ) .. param .. string.sub( sLine, nPos + 1 )
            nPos = nPos + 1
            recomplete()
            redraw()

        elseif sEvent == "paste" then
            -- Pasted text
            clear()
            sLine = string.sub( sLine, 1, nPos ) .. param .. string.sub( sLine, nPos + 1 )
            nPos = nPos + string.len( param )
            recomplete()
            redraw()

        elseif sEvent == "key" then
            if param == keys.enter then
                -- Enter
                if nCompletion then
                    clear()
                    uncomplete()
                    redraw()
                end
                break
                
            elseif param == keys.left then
                -- Left
                if nPos > 0 then
                    clear()
                    nPos = nPos - 1
                    recomplete()
                    redraw()
                end
                
            elseif param == keys.right then
                -- Right                
                if nPos < string.len(sLine) then
                    -- Move right
                    clear()
                    nPos = nPos + 1
                    recomplete()
                    redraw()
                else
                    -- Accept autocomplete
                    acceptCompletion()
                end

            elseif param == keys.up or param == keys.down then
                -- Up or down
                if nCompletion then
                    -- Cycle completions
                    clear()
                    if param == keys.up then
                        nCompletion = nCompletion - 1
                        if nCompletion < 1 then
                            nCompletion = #tCompletions
                        end
                    elseif param == keys.down then
                        nCompletion = nCompletion + 1
                        if nCompletion > #tCompletions then
                            nCompletion = 1
                        end
                    end
                    redraw()

                elseif _tHistory then
                    -- Cycle history
                    clear()
                    if param == keys.up then
                        -- Up
                        if nHistoryPos == nil then
                            if #_tHistory > 0 then
                                nHistoryPos = #_tHistory
                            end
                        elseif nHistoryPos > 1 then
                            nHistoryPos = nHistoryPos - 1
                        end
                    else
                        -- Down
                        if nHistoryPos == #_tHistory then
                            nHistoryPos = nil
                        elseif nHistoryPos ~= nil then
                            nHistoryPos = nHistoryPos + 1
                        end                        
                    end
                    if nHistoryPos then
                        sLine = _tHistory[nHistoryPos]
                        nPos = string.len( sLine ) 
                    else
                        sLine = ""
                        nPos = 0
                    end
                    uncomplete()
                    redraw()

                end

            elseif param == keys.backspace then
                -- Backspace
                if nPos > 0 then
                    clear()
                    sLine = string.sub( sLine, 1, nPos - 1 ) .. string.sub( sLine, nPos + 1 )
                    nPos = nPos - 1
                    recomplete()
                    redraw()
                end

            elseif param == keys.home then
                -- Home
                if nPos > 0 then
                    clear()
                    nPos = 0
                    recomplete()
                    redraw()
                end

            elseif param == keys.delete then
                -- Delete
                if nPos < string.len(sLine) then
                    clear()
                    sLine = string.sub( sLine, 1, nPos ) .. string.sub( sLine, nPos + 2 )                
                    recomplete()
                    redraw()
                end

            elseif param == keys["end"] then
                -- End
                if nPos < string.len(sLine ) then
                    clear()
                    nPos = string.len(sLine)
                    recomplete()
                    redraw()
                end

            elseif param == keys.tab then
                -- Tab (accept autocomplete)
                acceptCompletion()

            end

        elseif sEvent == "term_resize" then
            -- Terminal resized
            w = term.getSize()
            redraw()
				
				elseif sEvent == "mouse_click" and _MouseEvent then
					if nCompletion then
            clear()
            uncomplete()
            redraw()
          end
					usedMouse = true
					break
        end
    end

    local cx, cy = term.getCursorPos()
    term.setCursorBlink( false )
    term.setCursorPos( w + 1, cy )
    print()
		if sEvent == "mouse_click" then
			return sLine, param, _MouseX, _MouseY
		end
    return sLine
end

local theme = {}
if term.isColor() then
	theme.bg = colors.white
	theme.text = colors.black
	theme.hdbg = colors.blue
	theme.hdtext = colors.white
	theme.wrong = colors.red
	theme.input = colors.gray
	theme.activeinput = colors.lightGray
	theme.inputtext = colors.lightGray
	theme.activeinputtext = colors.white
	theme.yes = colors.lime
	theme.no = colors.red
	theme.btntext = colors.white
else
	theme.bg = colors.white
	theme.text = colors.black
	theme.hdbg = colors.gray
	theme.hdtext = colors.white
	theme.wrong = colors.black
	theme.input = colors.gray
	theme.activeinput = colors.lightGray
	theme.inputtext = colors.white
	theme.activeinputtext = colors.black
	theme.yes = colors.lightGray
	theme.no = colors.gray
	theme.btntext = colors.white
end

local oldPull = os.pullEvent
os.pullEvent = os.pullEventRaw

local username = ""
local password = ""
local repeatpw = ""
local mouse,mx,my

local w,h = term.getSize()

if not get("accounts") then
	local exit = false
	set("conf","salt",sha256(tostring(os.time()+os.day())))
	while not exit do
		term.setBackgroundColor(theme.bg)
		term.clear()
		paintutils.drawLine(1,1,w,1,theme.hdbg)
		term.setTextColor(theme.hdtext)
		term.setBackgroundColor(theme.hdbg)
		term.setCursorPos(2,1)
		term.write("SertexSecurity 3.0 beta")

		term.setCursorPos(2,4)
		term.setBackgroundColor(theme.bg)
		term.setTextColor(theme.text)
		print((function() if not term.isColor() then return "[1] " end return "" end)().."Username")
		term.setCursorPos(2,8)
		print((function() if not term.isColor() then return "[2] " end return "" end)().."Password")
		term.setCursorPos(2,12)
		print((function() if not term.isColor() then return "[3] " end return "" end)().."Repeat Password")
		if term.isColor() then
			term.setCursorPos(w-10,h-1)
			print("Unlock >")
		else
			term.setCursorPos(w-13,h-1)
			print("[4] Unlock >")
		end

		paintutils.drawLine(2,5,w-5,5,theme.input)
		paintutils.drawLine(2,9,w-5,9,theme.input)
		paintutils.drawLine(2,13,w-5,13,theme.input)
		
		local lExit = false

		os.queueEvent("mouse_click",1,2,5) --first input

		while not lExit do
			local ev={os.pullEvent()}
			if ev[1] == "mouse_click" then
				local x,y = ev[3], ev[4]
				if y == 5 and (x>=2 and x<=w-5) then
					local curr = term.current()
					local inp = window.create(term.current(), 2,5,w-6,1,true)
					term.redirect(inp)
					term.setBackgroundColor(theme.activeinput)
					term.setTextColor(theme.activeinputtext)
					term.clear()
					term.setCursorPos(1,1)
					username, mouse, mx,my = read(nil,nil,nil,true,username)
					term.setBackgroundColor(theme.input)
					term.setTextColor(theme.inputtext)
					term.clear()
					term.setCursorPos(1,1)
					term.write(username)
					term.redirect(curr)
					if mouse then
						os.queueEvent("mouse_click",1,mx,my)
					else
						os.queueEvent("mouse_click",1,2,9)
					end
				elseif y == 9 and (x>=2 and x<=w-5) then
					local curr = term.current()
					local inp = window.create(term.current(), 2,9,w-6,1,true)
					term.redirect(inp)
					term.setBackgroundColor(theme.activeinput)
					term.setTextColor(theme.activeinputtext)
					term.clear()
					term.setCursorPos(1,1)
					password, mouse, mx,my = read("*",nil,nil,true,password)
					term.setBackgroundColor(theme.input)
					term.setTextColor(theme.inputtext)
					term.clear()
					term.setCursorPos(1,1)
					term.write(string.rep("*",password:len()))
					term.redirect(curr)
					if mouse then
						os.queueEvent("mouse_click",1,mx,my)
					else
						os.queueEvent("mouse_click",1,2,13)
					end
				elseif y == 13 and (x>=2 and x<=w-5) then
					local curr = term.current()
					local inp = window.create(term.current(), 2,13,w-6,1,true)
					term.redirect(inp)
					term.setBackgroundColor(theme.activeinput)
					term.setTextColor(theme.activeinputtext)
					term.clear()
					term.setCursorPos(1,1)
					repeatpw, mouse, mx,my = read("*",nil,nil,true,repeatpw)
					term.setBackgroundColor(theme.input)
					term.setTextColor(theme.inputtext)
					term.clear()
					term.setCursorPos(1,1)
					term.write(string.rep("*",repeatpw:len()))
					term.redirect(curr)
					if mouse then
						os.queueEvent("mouse_click",1,mx,my)
					else
						os.queueEvent("mouse_click",1,w-13,h-1)
					end
				elseif y == h-1 and (w-13 and x<=w-5) then
					if repeatpw == password then
						set("accounts",username,sha256(get("conf","salt")..sha256(password)..sha256(username)))
						local accounts = {}
						for k,v in pairs(list("accounts")) do
							table.insert(accounts,k)
						end
						term.setBackgroundColor(theme.bg)
						term.clear()
						paintutils.drawLine(1,1,w,1,theme.hdbg)
						term.setTextColor(theme.hdtext)
						term.setBackgroundColor(theme.hdbg)
						term.setCursorPos(2,1)
						term.write("SertexSecurity 3.0 beta")

						term.setCursorPos(2,4)
						term.setBackgroundColor(theme.bg)
						term.setTextColor(theme.text)
						print("Create another account?")
						paintutils.drawLine(2,6,6,6,theme.yes)
						paintutils.drawLine(9,6,12,6,theme.no)
						term.setCursorPos(3,6)
						term.setTextColor(theme.btntext)
						term.setBackgroundColor(theme.yes)
						write("Yes")
						term.setCursorPos(10,6)
						term.setTextColor(theme.btntext)
						term.setBackgroundColor(theme.no)
						write("No")
						term.setBackgroundColor(theme.bg)
						term.setTextColor(theme.text)
						local curr = term.current()
						local nw = window.create(curr,2,9,w-2,h-9,true)
						nw.setBackgroundColor(theme.bg)
						nw.setTextColor(theme.text)
						nw.clear()
						nw.setCursorPos(1,1)
						term.redirect(nw)
						write("Accounts: "..table.concat(accounts,", "))
						term.redirect(curr)
						while true do
							local e = {os.pullEvent()}
							if e[1] == "mouse_click" then
								local x,y = e[3],e[4]
								if y == 6 then
									if x >= 2 and x <= 6 then
										lExit = true
										username = ""
										password = ""
										repeatpw = ""
										break
									elseif x >= 9 and x <= 12 then
										exit = true
										lExit = true
										break
									end
								end
							end
						end
					else
						term.setCursorPos(2,16)
						term.setTextColor(theme.wrong)
						term.setBackgroundColor(theme.bg)
						print("Passwords do not match!")
					end
				end
			elseif ev[1] == "char" then
				local c = ev[2]
				if c == "1" then
					os.queueEvent("mouse_click",1,2,5)
				elseif c == "2" then
					os.queueEvent("mouse_click",1,2,9)
				elseif c == "3" then
					os.queueEvent("mouse_click",1,2,13)
				elseif c == "4" then
					os.queueEvent("mouse_click",1,w-13,h-1)
				end
			end
		end
	end
	if settings then
		settings.set("shell.allow_disk_startup",false)
		settings.save(".settings")
	end
	os.pullEvent = oldPull
	term.setBackgroundColor(colors.black)
	term.setTextColor(colors.white)
	term.clear()
	term.setCursorPos(1,1)
	print("Account(s) created!")
	if settings then
		print("Setting \"shell.allow_disk_startup\" has been disabled!")
	end
	if os.getComputerLabel() then
		printError("It is recommended to clear label!")
	end
	return
end

if not get("conf","salt") then
	set("conf","salt",sha256(tostring(os.time()+os.day())))
end

term.setBackgroundColor(theme.bg)
term.clear()
paintutils.drawLine(1,1,w,1,theme.hdbg)
term.setTextColor(theme.hdtext)
term.setBackgroundColor(theme.hdbg)
term.setCursorPos(2,1)
term.write("SertexSecurity 3.0 beta")

term.setCursorPos(2,4)
term.setBackgroundColor(theme.bg)
term.setTextColor(theme.text)
print((function() if not term.isColor() then return "[1] " end return "" end)().."Username")
term.setCursorPos(2,8)
print((function() if not term.isColor() then return "[2] " end return "" end)().."Password")
if term.isColor() then
	term.setCursorPos(w-10,h-1)
	print("Unlock >")
else
	term.setCursorPos(w-13,h-1)
	print("[3] Unlock >")
end

paintutils.drawLine(2,5,w-5,5,theme.input)
paintutils.drawLine(2,9,w-5,9,theme.input)

os.queueEvent("mouse_click",1,2,5) --first input

while true do
	local ev={os.pullEvent()}
	if ev[1] == "mouse_click" then
		local x,y = ev[3], ev[4]
		if y == 5 and (x>=2 and x<=w-5) then
			local curr = term.current()
			local inp = window.create(term.current(), 2,5,w-6,1,true)
			term.redirect(inp)
			term.setBackgroundColor(theme.activeinput)
			term.setTextColor(theme.activeinputtext)
			term.clear()
			term.setCursorPos(1,1)
			username, mouse, mx,my = read(nil,nil,nil,true,username)
			term.setBackgroundColor(theme.input)
			term.setTextColor(theme.inputtext)
			term.clear()
			term.setCursorPos(1,1)
			term.write(username)
			term.redirect(curr)
			if mouse then
				os.queueEvent("mouse_click",1,mx,my)
			else
				os.queueEvent("mouse_click",1,2,9)
			end
		elseif y == 9 and (x>=2 and x<=w-5) then
			local curr = term.current()
			local inp = window.create(term.current(), 2,9,w-6,1,true)
			term.redirect(inp)
			term.setBackgroundColor(theme.activeinput)
			term.setTextColor(theme.activeinputtext)
			term.clear()
			term.setCursorPos(1,1)
			password, mouse, mx,my = read("*",nil,nil,true,password)
			term.setBackgroundColor(theme.input)
			term.setTextColor(theme.inputtext)
			term.clear()
			term.setCursorPos(1,1)
			term.write(string.rep("*",password:len()))
			term.redirect(curr)
			if mouse then
				os.queueEvent("mouse_click",1,mx,my)
			else
				os.queueEvent("mouse_click",1,w-13,h-1)
			end
		elseif y == h-1 and (w-13 and x<=w-5) then
			if get("accounts",username) then
				if sha256(get("conf","salt")..sha256(password)..sha256(username)) == get("accounts",username) then
					os.pullEvent = oldPull
					term.setBackgroundColor(colors.black)
					term.setTextColor(colors.white)
					term.clear()
					term.setCursorPos(1,1)
					if os.getComputerLabel() then
						printError("Warning: Label is set!")
					end
					if settings and settings.get("shell.allow_disk_startup") then
						printError("Warning: Setting \"shell.allow_disk_startup\" is enabled!")
					end
					return
				else
					term.setCursorPos(2,12)
					term.setTextColor(theme.wrong)
					term.setBackgroundColor(theme.bg)
					print("Wrong username or password!")
				end
			else
				term.setCursorPos(2,12)
				term.setTextColor(theme.wrong)
				term.setBackgroundColor(theme.bg)
				print("Wrong username or password!")
			end
		end
	elseif ev[1] == "char" then
		local c = ev[2]
		if c == "1" then
			os.queueEvent("mouse_click",1,2,5)
		elseif c == "2" then
			os.queueEvent("mouse_click",1,2,9)
		elseif c == "3" then
			os.queueEvent("mouse_click",1,w-13,h-1)
		end
	end
end
