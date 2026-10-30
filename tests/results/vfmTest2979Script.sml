Theory vfmTest2979[no_sig_docs]
Ancestors vfmTestDefs2979
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2979_0.nsv", "result2979_1.nsv", "result2979_2.nsv", "result2979_3.nsv", "result2979_4.nsv", "result2979_5.nsv", "result2979_6.nsv", "result2979_7.nsv", "result2979_8.nsv", "result2979_9.nsv", "result2979_10.nsv", "result2979_11.nsv", "result2979_12.nsv", "result2979_13.nsv", "result2979_14.nsv", "result2979_15.nsv", "result2979_16.nsv", "result2979_17.nsv", "result2979_18.nsv", "result2979_19.nsv", "result2979_20.nsv", "result2979_21.nsv", "result2979_22.nsv", "result2979_23.nsv", "result2979_24.nsv", "result2979_25.nsv", "result2979_26.nsv", "result2979_27.nsv", "result2979_28.nsv", "result2979_29.nsv", "result2979_30.nsv", "result2979_31.nsv", "result2979_32.nsv", "result2979_33.nsv", "result2979_34.nsv", "result2979_35.nsv"];
val thyn = "vfmTestDefs2979";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
