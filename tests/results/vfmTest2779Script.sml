Theory vfmTest2779[no_sig_docs]
Ancestors vfmTestDefs2779
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2779_0.nsv", "result2779_1.nsv", "result2779_2.nsv", "result2779_3.nsv"];
val thyn = "vfmTestDefs2779";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
