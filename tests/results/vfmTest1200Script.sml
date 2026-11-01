Theory vfmTest1200[no_sig_docs]
Ancestors vfmTestDefs1200
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1200_0.nsv", "result1200_1.nsv", "result1200_2.nsv", "result1200_3.nsv", "result1200_4.nsv", "result1200_5.nsv", "result1200_6.nsv", "result1200_7.nsv", "result1200_8.nsv", "result1200_9.nsv", "result1200_10.nsv", "result1200_11.nsv", "result1200_12.nsv", "result1200_13.nsv", "result1200_14.nsv", "result1200_15.nsv", "result1200_16.nsv", "result1200_17.nsv", "result1200_18.nsv", "result1200_19.nsv", "result1200_20.nsv", "result1200_21.nsv", "result1200_22.nsv", "result1200_23.nsv", "result1200_24.nsv", "result1200_25.nsv", "result1200_26.nsv", "result1200_27.nsv", "result1200_28.nsv", "result1200_29.nsv"];
val thyn = "vfmTestDefs1200";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
