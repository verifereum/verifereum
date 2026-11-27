Theory vfmTest0628[no_sig_docs]
Ancestors vfmTestDefs0628
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0628_0.nsv", "result0628_1.nsv", "result0628_2.nsv", "result0628_3.nsv", "result0628_4.nsv", "result0628_5.nsv", "result0628_6.nsv", "result0628_7.nsv", "result0628_8.nsv", "result0628_9.nsv", "result0628_10.nsv", "result0628_11.nsv", "result0628_12.nsv", "result0628_13.nsv", "result0628_14.nsv", "result0628_15.nsv", "result0628_16.nsv", "result0628_17.nsv", "result0628_18.nsv", "result0628_19.nsv", "result0628_20.nsv", "result0628_21.nsv", "result0628_22.nsv", "result0628_23.nsv", "result0628_24.nsv", "result0628_25.nsv", "result0628_26.nsv", "result0628_27.nsv", "result0628_28.nsv", "result0628_29.nsv", "result0628_30.nsv", "result0628_31.nsv", "result0628_32.nsv", "result0628_33.nsv"];
val thyn = "vfmTestDefs0628";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
