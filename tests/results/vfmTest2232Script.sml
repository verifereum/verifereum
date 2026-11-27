Theory vfmTest2232[no_sig_docs]
Ancestors vfmTestDefs2232
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2232_0.nsv", "result2232_1.nsv", "result2232_2.nsv", "result2232_3.nsv", "result2232_4.nsv", "result2232_5.nsv", "result2232_6.nsv", "result2232_7.nsv", "result2232_8.nsv", "result2232_9.nsv", "result2232_10.nsv", "result2232_11.nsv", "result2232_12.nsv", "result2232_13.nsv", "result2232_14.nsv", "result2232_15.nsv", "result2232_16.nsv", "result2232_17.nsv", "result2232_18.nsv", "result2232_19.nsv", "result2232_20.nsv", "result2232_21.nsv", "result2232_22.nsv", "result2232_23.nsv", "result2232_24.nsv", "result2232_25.nsv", "result2232_26.nsv", "result2232_27.nsv", "result2232_28.nsv", "result2232_29.nsv", "result2232_30.nsv", "result2232_31.nsv", "result2232_32.nsv"];
val thyn = "vfmTestDefs2232";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
