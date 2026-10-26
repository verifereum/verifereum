Theory vfmTest2814[no_sig_docs]
Ancestors vfmTestDefs2814
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2814_0.nsv", "result2814_1.nsv", "result2814_2.nsv", "result2814_3.nsv", "result2814_4.nsv", "result2814_5.nsv", "result2814_6.nsv", "result2814_7.nsv", "result2814_8.nsv", "result2814_9.nsv", "result2814_10.nsv", "result2814_11.nsv", "result2814_12.nsv", "result2814_13.nsv", "result2814_14.nsv", "result2814_15.nsv", "result2814_16.nsv", "result2814_17.nsv", "result2814_18.nsv", "result2814_19.nsv", "result2814_20.nsv", "result2814_21.nsv", "result2814_22.nsv", "result2814_23.nsv", "result2814_24.nsv", "result2814_25.nsv", "result2814_26.nsv", "result2814_27.nsv", "result2814_28.nsv", "result2814_29.nsv"];
val thyn = "vfmTestDefs2814";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
