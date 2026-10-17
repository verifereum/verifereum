Theory vfmTest2344[no_sig_docs]
Ancestors vfmTestDefs2344
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2344_0.nsv", "result2344_1.nsv", "result2344_2.nsv"];
val thyn = "vfmTestDefs2344";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
