Theory vfmTest0617[no_sig_docs]
Ancestors vfmTestDefs0617
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0617_0.nsv", "result0617_1.nsv", "result0617_2.nsv", "result0617_3.nsv", "result0617_4.nsv", "result0617_5.nsv", "result0617_6.nsv", "result0617_7.nsv"];
val thyn = "vfmTestDefs0617";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
