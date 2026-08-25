Theory vfmTest2079[no_sig_docs]
Ancestors vfmTestDefs2079
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2079_0.nsv", "result2079_1.nsv", "result2079_2.nsv", "result2079_3.nsv", "result2079_4.nsv", "result2079_5.nsv", "result2079_6.nsv", "result2079_7.nsv", "result2079_8.nsv", "result2079_9.nsv", "result2079_10.nsv", "result2079_11.nsv", "result2079_12.nsv", "result2079_13.nsv", "result2079_14.nsv", "result2079_15.nsv", "result2079_16.nsv", "result2079_17.nsv", "result2079_18.nsv", "result2079_19.nsv", "result2079_20.nsv", "result2079_21.nsv", "result2079_22.nsv", "result2079_23.nsv", "result2079_24.nsv", "result2079_25.nsv", "result2079_26.nsv", "result2079_27.nsv", "result2079_28.nsv", "result2079_29.nsv", "result2079_30.nsv"];
val thyn = "vfmTestDefs2079";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
