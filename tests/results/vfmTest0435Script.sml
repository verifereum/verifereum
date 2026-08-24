Theory vfmTest0435[no_sig_docs]
Ancestors vfmTestDefs0435
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0435_0.nsv", "result0435_1.nsv", "result0435_2.nsv", "result0435_3.nsv", "result0435_4.nsv", "result0435_5.nsv"];
val thyn = "vfmTestDefs0435";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
