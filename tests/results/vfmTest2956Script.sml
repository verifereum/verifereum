Theory vfmTest2956[no_sig_docs]
Ancestors vfmTestDefs2956
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2956_0.nsv", "result2956_1.nsv", "result2956_2.nsv", "result2956_3.nsv", "result2956_4.nsv", "result2956_5.nsv", "result2956_6.nsv", "result2956_7.nsv", "result2956_8.nsv", "result2956_9.nsv", "result2956_10.nsv", "result2956_11.nsv", "result2956_12.nsv", "result2956_13.nsv", "result2956_14.nsv", "result2956_15.nsv", "result2956_16.nsv", "result2956_17.nsv", "result2956_18.nsv", "result2956_19.nsv", "result2956_20.nsv", "result2956_21.nsv", "result2956_22.nsv", "result2956_23.nsv", "result2956_24.nsv", "result2956_25.nsv"];
val thyn = "vfmTestDefs2956";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
