Theory vfmTest0318[no_sig_docs]
Ancestors vfmTestDefs0318
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0318_0.nsv", "result0318_1.nsv", "result0318_2.nsv", "result0318_3.nsv", "result0318_4.nsv", "result0318_5.nsv", "result0318_6.nsv", "result0318_7.nsv", "result0318_8.nsv", "result0318_9.nsv", "result0318_10.nsv", "result0318_11.nsv", "result0318_12.nsv", "result0318_13.nsv", "result0318_14.nsv", "result0318_15.nsv", "result0318_16.nsv", "result0318_17.nsv", "result0318_18.nsv", "result0318_19.nsv", "result0318_20.nsv"];
val thyn = "vfmTestDefs0318";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
