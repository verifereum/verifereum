Theory vfmTest2620[no_sig_docs]
Ancestors vfmTestDefs2620
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2620_0.nsv", "result2620_1.nsv", "result2620_2.nsv", "result2620_3.nsv"];
val thyn = "vfmTestDefs2620";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
