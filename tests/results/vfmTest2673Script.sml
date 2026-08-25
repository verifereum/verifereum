Theory vfmTest2673[no_sig_docs]
Ancestors vfmTestDefs2673
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2673_0.nsv", "result2673_1.nsv", "result2673_2.nsv", "result2673_3.nsv"];
val thyn = "vfmTestDefs2673";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
