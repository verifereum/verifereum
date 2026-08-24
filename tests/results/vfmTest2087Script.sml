Theory vfmTest2087[no_sig_docs]
Ancestors vfmTestDefs2087
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2087_0.nsv", "result2087_1.nsv"];
val thyn = "vfmTestDefs2087";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
