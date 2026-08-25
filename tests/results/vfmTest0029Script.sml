Theory vfmTest0029[no_sig_docs]
Ancestors vfmTestDefs0029
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0029_0.nsv", "result0029_1.nsv", "result0029_2.nsv", "result0029_3.nsv", "result0029_4.nsv", "result0029_5.nsv", "result0029_6.nsv", "result0029_7.nsv", "result0029_8.nsv", "result0029_9.nsv", "result0029_10.nsv", "result0029_11.nsv", "result0029_12.nsv", "result0029_13.nsv", "result0029_14.nsv", "result0029_15.nsv", "result0029_16.nsv", "result0029_17.nsv", "result0029_18.nsv", "result0029_19.nsv", "result0029_20.nsv", "result0029_21.nsv", "result0029_22.nsv", "result0029_23.nsv"];
val thyn = "vfmTestDefs0029";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
