Theory vfmTest0376[no_sig_docs]
Ancestors vfmTestDefs0376
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0376_0.nsv", "result0376_1.nsv", "result0376_2.nsv", "result0376_3.nsv", "result0376_4.nsv", "result0376_5.nsv", "result0376_6.nsv", "result0376_7.nsv", "result0376_8.nsv", "result0376_9.nsv", "result0376_10.nsv", "result0376_11.nsv", "result0376_12.nsv", "result0376_13.nsv", "result0376_14.nsv", "result0376_15.nsv"];
val thyn = "vfmTestDefs0376";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
