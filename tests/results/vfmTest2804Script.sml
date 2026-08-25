Theory vfmTest2804[no_sig_docs]
Ancestors vfmTestDefs2804
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2804_0.nsv", "result2804_1.nsv", "result2804_2.nsv", "result2804_3.nsv"];
val thyn = "vfmTestDefs2804";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
