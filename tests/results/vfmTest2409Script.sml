Theory vfmTest2409[no_sig_docs]
Ancestors vfmTestDefs2409
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2409_0.nsv", "result2409_1.nsv", "result2409_2.nsv", "result2409_3.nsv", "result2409_4.nsv"];
val thyn = "vfmTestDefs2409";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
