Theory vfmTest0774[no_sig_docs]
Ancestors vfmTestDefs0774
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0774_0.nsv", "result0774_1.nsv", "result0774_2.nsv", "result0774_3.nsv", "result0774_4.nsv", "result0774_5.nsv", "result0774_6.nsv", "result0774_7.nsv", "result0774_8.nsv", "result0774_9.nsv", "result0774_10.nsv", "result0774_11.nsv", "result0774_12.nsv", "result0774_13.nsv", "result0774_14.nsv", "result0774_15.nsv", "result0774_16.nsv", "result0774_17.nsv", "result0774_18.nsv", "result0774_19.nsv", "result0774_20.nsv", "result0774_21.nsv", "result0774_22.nsv", "result0774_23.nsv", "result0774_24.nsv", "result0774_25.nsv", "result0774_26.nsv", "result0774_27.nsv", "result0774_28.nsv", "result0774_29.nsv", "result0774_30.nsv", "result0774_31.nsv"];
val thyn = "vfmTestDefs0774";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
