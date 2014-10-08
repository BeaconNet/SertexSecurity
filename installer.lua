os.pullEvent = os.pullEventRaw

--https://raw.githubusercontent.com/Sertex-Team/SertexSecurity/master/security.lua

if fs.exists("/startup") then
  fs.rename("startup", "startup.bak")
elseif fs.exists("/startup") and fs.exists("/startup.bak")
  fs.delete("startup.bak")
  fs.rename("startup", "startup.bak")
end

