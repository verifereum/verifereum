Theory vfmTest0752[no_sig_docs]
Ancestors vfmTestDefs0752
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0752_0.nsv", "result0752_1.nsv", "result0752_2.nsv", "result0752_3.nsv", "result0752_4.nsv", "result0752_5.nsv", "result0752_6.nsv", "result0752_7.nsv", "result0752_8.nsv", "result0752_9.nsv", "result0752_10.nsv", "result0752_11.nsv", "result0752_12.nsv", "result0752_13.nsv", "result0752_14.nsv", "result0752_15.nsv", "result0752_16.nsv", "result0752_17.nsv", "result0752_18.nsv", "result0752_19.nsv", "result0752_20.nsv", "result0752_21.nsv", "result0752_22.nsv", "result0752_23.nsv", "result0752_24.nsv", "result0752_25.nsv", "result0752_26.nsv", "result0752_27.nsv", "result0752_28.nsv", "result0752_29.nsv", "result0752_30.nsv", "result0752_31.nsv", "result0752_32.nsv", "result0752_33.nsv", "result0752_34.nsv", "result0752_35.nsv"];
val thyn = "vfmTestDefs0752";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
