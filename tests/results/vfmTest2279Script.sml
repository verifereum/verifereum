Theory vfmTest2279[no_sig_docs]
Ancestors vfmTestDefs2279
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2279_0.nsv", "result2279_1.nsv", "result2279_2.nsv", "result2279_3.nsv", "result2279_4.nsv", "result2279_5.nsv", "result2279_6.nsv", "result2279_7.nsv", "result2279_8.nsv", "result2279_9.nsv", "result2279_10.nsv", "result2279_11.nsv", "result2279_12.nsv", "result2279_13.nsv", "result2279_14.nsv", "result2279_15.nsv", "result2279_16.nsv", "result2279_17.nsv", "result2279_18.nsv", "result2279_19.nsv", "result2279_20.nsv", "result2279_21.nsv", "result2279_22.nsv"];
val thyn = "vfmTestDefs2279";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
