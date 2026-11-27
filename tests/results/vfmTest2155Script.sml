Theory vfmTest2155[no_sig_docs]
Ancestors vfmTestDefs2155
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2155_0.nsv", "result2155_1.nsv", "result2155_2.nsv", "result2155_3.nsv", "result2155_4.nsv", "result2155_5.nsv", "result2155_6.nsv", "result2155_7.nsv", "result2155_8.nsv", "result2155_9.nsv", "result2155_10.nsv", "result2155_11.nsv", "result2155_12.nsv", "result2155_13.nsv", "result2155_14.nsv", "result2155_15.nsv", "result2155_16.nsv", "result2155_17.nsv", "result2155_18.nsv", "result2155_19.nsv", "result2155_20.nsv", "result2155_21.nsv", "result2155_22.nsv", "result2155_23.nsv", "result2155_24.nsv", "result2155_25.nsv", "result2155_26.nsv", "result2155_27.nsv", "result2155_28.nsv", "result2155_29.nsv", "result2155_30.nsv", "result2155_31.nsv", "result2155_32.nsv", "result2155_33.nsv", "result2155_34.nsv", "result2155_35.nsv"];
val thyn = "vfmTestDefs2155";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
