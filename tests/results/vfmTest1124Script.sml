Theory vfmTest1124[no_sig_docs]
Ancestors vfmTestDefs1124
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1124_0.nsv", "result1124_1.nsv"];
val thyn = "vfmTestDefs1124";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
