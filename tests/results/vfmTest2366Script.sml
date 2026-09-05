Theory vfmTest2366[no_sig_docs]
Ancestors vfmTestDefs2366
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2366_0.nsv", "result2366_1.nsv", "result2366_2.nsv"];
val thyn = "vfmTestDefs2366";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
