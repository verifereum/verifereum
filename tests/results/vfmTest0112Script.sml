Theory vfmTest0112[no_sig_docs]
Ancestors vfmTestDefs0112
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0112_0.nsv", "result0112_1.nsv", "result0112_2.nsv", "result0112_3.nsv", "result0112_4.nsv", "result0112_5.nsv", "result0112_6.nsv", "result0112_7.nsv", "result0112_8.nsv", "result0112_9.nsv", "result0112_10.nsv", "result0112_11.nsv", "result0112_12.nsv", "result0112_13.nsv", "result0112_14.nsv", "result0112_15.nsv", "result0112_16.nsv", "result0112_17.nsv", "result0112_18.nsv", "result0112_19.nsv", "result0112_20.nsv"];
val thyn = "vfmTestDefs0112";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
