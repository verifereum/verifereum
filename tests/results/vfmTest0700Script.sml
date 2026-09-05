Theory vfmTest0700[no_sig_docs]
Ancestors vfmTestDefs0700
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0700_0.nsv", "result0700_1.nsv", "result0700_2.nsv", "result0700_3.nsv", "result0700_4.nsv", "result0700_5.nsv", "result0700_6.nsv", "result0700_7.nsv", "result0700_8.nsv", "result0700_9.nsv", "result0700_10.nsv", "result0700_11.nsv", "result0700_12.nsv", "result0700_13.nsv", "result0700_14.nsv", "result0700_15.nsv", "result0700_16.nsv", "result0700_17.nsv", "result0700_18.nsv", "result0700_19.nsv", "result0700_20.nsv", "result0700_21.nsv", "result0700_22.nsv", "result0700_23.nsv", "result0700_24.nsv", "result0700_25.nsv", "result0700_26.nsv", "result0700_27.nsv", "result0700_28.nsv", "result0700_29.nsv"];
val thyn = "vfmTestDefs0700";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
