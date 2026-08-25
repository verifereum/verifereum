Theory vfmTest0283[no_sig_docs]
Ancestors vfmTestDefs0283
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0283_0.nsv", "result0283_1.nsv", "result0283_2.nsv", "result0283_3.nsv", "result0283_4.nsv", "result0283_5.nsv", "result0283_6.nsv", "result0283_7.nsv"];
val thyn = "vfmTestDefs0283";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
