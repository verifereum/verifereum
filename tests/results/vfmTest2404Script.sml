Theory vfmTest2404[no_sig_docs]
Ancestors vfmTestDefs2404
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2404_0.nsv", "result2404_1.nsv", "result2404_2.nsv", "result2404_3.nsv", "result2404_4.nsv", "result2404_5.nsv", "result2404_6.nsv", "result2404_7.nsv", "result2404_8.nsv", "result2404_9.nsv", "result2404_10.nsv", "result2404_11.nsv", "result2404_12.nsv", "result2404_13.nsv", "result2404_14.nsv", "result2404_15.nsv", "result2404_16.nsv", "result2404_17.nsv", "result2404_18.nsv", "result2404_19.nsv", "result2404_20.nsv", "result2404_21.nsv", "result2404_22.nsv", "result2404_23.nsv", "result2404_24.nsv", "result2404_25.nsv", "result2404_26.nsv", "result2404_27.nsv", "result2404_28.nsv", "result2404_29.nsv", "result2404_30.nsv", "result2404_31.nsv"];
val thyn = "vfmTestDefs2404";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
