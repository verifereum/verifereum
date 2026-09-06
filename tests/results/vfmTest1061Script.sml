Theory vfmTest1061[no_sig_docs]
Ancestors vfmTestDefs1061
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1061_0.nsv", "result1061_1.nsv"];
val thyn = "vfmTestDefs1061";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
