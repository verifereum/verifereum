Theory vfmTest0612[no_sig_docs]
Ancestors vfmTestDefs0612
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0612_0.nsv", "result0612_1.nsv", "result0612_2.nsv", "result0612_3.nsv", "result0612_4.nsv", "result0612_5.nsv", "result0612_6.nsv", "result0612_7.nsv", "result0612_8.nsv", "result0612_9.nsv", "result0612_10.nsv", "result0612_11.nsv", "result0612_12.nsv", "result0612_13.nsv", "result0612_14.nsv", "result0612_15.nsv", "result0612_16.nsv", "result0612_17.nsv", "result0612_18.nsv", "result0612_19.nsv", "result0612_20.nsv", "result0612_21.nsv", "result0612_22.nsv", "result0612_23.nsv"];
val thyn = "vfmTestDefs0612";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
