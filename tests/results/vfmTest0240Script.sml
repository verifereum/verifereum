Theory vfmTest0240[no_sig_docs]
Ancestors vfmTestDefs0240
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0240_0.nsv", "result0240_1.nsv", "result0240_2.nsv", "result0240_3.nsv", "result0240_4.nsv", "result0240_5.nsv", "result0240_6.nsv", "result0240_7.nsv", "result0240_8.nsv", "result0240_9.nsv", "result0240_10.nsv", "result0240_11.nsv", "result0240_12.nsv", "result0240_13.nsv", "result0240_14.nsv", "result0240_15.nsv", "result0240_16.nsv", "result0240_17.nsv", "result0240_18.nsv", "result0240_19.nsv", "result0240_20.nsv", "result0240_21.nsv", "result0240_22.nsv", "result0240_23.nsv", "result0240_24.nsv", "result0240_25.nsv", "result0240_26.nsv", "result0240_27.nsv", "result0240_28.nsv", "result0240_29.nsv", "result0240_30.nsv", "result0240_31.nsv"];
val thyn = "vfmTestDefs0240";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
