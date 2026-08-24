Theory vfmTest2752[no_sig_docs]
Ancestors vfmTestDefs2752
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2752_0.nsv", "result2752_1.nsv", "result2752_2.nsv", "result2752_3.nsv"];
val thyn = "vfmTestDefs2752";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
