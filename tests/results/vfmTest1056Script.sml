Theory vfmTest1056[no_sig_docs]
Ancestors vfmTestDefs1056
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1056_0.nsv", "result1056_1.nsv", "result1056_2.nsv", "result1056_3.nsv"];
val thyn = "vfmTestDefs1056";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
