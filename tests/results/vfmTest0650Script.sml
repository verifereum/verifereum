Theory vfmTest0650[no_sig_docs]
Ancestors vfmTestDefs0650
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0650_0.nsv", "result0650_1.nsv", "result0650_2.nsv", "result0650_3.nsv", "result0650_4.nsv", "result0650_5.nsv", "result0650_6.nsv", "result0650_7.nsv", "result0650_8.nsv", "result0650_9.nsv", "result0650_10.nsv", "result0650_11.nsv", "result0650_12.nsv", "result0650_13.nsv", "result0650_14.nsv", "result0650_15.nsv", "result0650_16.nsv", "result0650_17.nsv", "result0650_18.nsv", "result0650_19.nsv", "result0650_20.nsv", "result0650_21.nsv", "result0650_22.nsv", "result0650_23.nsv", "result0650_24.nsv", "result0650_25.nsv", "result0650_26.nsv", "result0650_27.nsv", "result0650_28.nsv", "result0650_29.nsv", "result0650_30.nsv", "result0650_31.nsv"];
val thyn = "vfmTestDefs0650";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
