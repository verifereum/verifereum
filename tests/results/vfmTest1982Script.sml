Theory vfmTest1982[no_sig_docs]
Ancestors vfmTestDefs1982
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1982_0.nsv", "result1982_1.nsv"];
val thyn = "vfmTestDefs1982";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
