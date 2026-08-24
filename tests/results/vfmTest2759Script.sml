Theory vfmTest2759[no_sig_docs]
Ancestors vfmTestDefs2759
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2759_0.nsv", "result2759_1.nsv", "result2759_2.nsv", "result2759_3.nsv"];
val thyn = "vfmTestDefs2759";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
