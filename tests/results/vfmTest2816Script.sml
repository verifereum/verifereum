Theory vfmTest2816[no_sig_docs]
Ancestors vfmTestDefs2816
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2816_0.nsv", "result2816_1.nsv", "result2816_2.nsv", "result2816_3.nsv", "result2816_4.nsv", "result2816_5.nsv", "result2816_6.nsv", "result2816_7.nsv", "result2816_8.nsv", "result2816_9.nsv", "result2816_10.nsv", "result2816_11.nsv", "result2816_12.nsv", "result2816_13.nsv", "result2816_14.nsv", "result2816_15.nsv", "result2816_16.nsv", "result2816_17.nsv", "result2816_18.nsv", "result2816_19.nsv", "result2816_20.nsv", "result2816_21.nsv", "result2816_22.nsv", "result2816_23.nsv", "result2816_24.nsv", "result2816_25.nsv", "result2816_26.nsv", "result2816_27.nsv", "result2816_28.nsv", "result2816_29.nsv"];
val thyn = "vfmTestDefs2816";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
