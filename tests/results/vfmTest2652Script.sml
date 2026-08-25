Theory vfmTest2652[no_sig_docs]
Ancestors vfmTestDefs2652
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2652_0.nsv", "result2652_1.nsv", "result2652_2.nsv", "result2652_3.nsv"];
val thyn = "vfmTestDefs2652";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
