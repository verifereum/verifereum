Theory vfmTest2425[no_sig_docs]
Ancestors vfmTestDefs2425
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2425_0.nsv", "result2425_1.nsv", "result2425_2.nsv", "result2425_3.nsv", "result2425_4.nsv", "result2425_5.nsv", "result2425_6.nsv", "result2425_7.nsv", "result2425_8.nsv", "result2425_9.nsv", "result2425_10.nsv", "result2425_11.nsv", "result2425_12.nsv", "result2425_13.nsv", "result2425_14.nsv", "result2425_15.nsv", "result2425_16.nsv", "result2425_17.nsv", "result2425_18.nsv", "result2425_19.nsv", "result2425_20.nsv", "result2425_21.nsv", "result2425_22.nsv", "result2425_23.nsv", "result2425_24.nsv", "result2425_25.nsv", "result2425_26.nsv", "result2425_27.nsv", "result2425_28.nsv", "result2425_29.nsv"];
val thyn = "vfmTestDefs2425";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
