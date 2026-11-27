Theory vfmTest2165[no_sig_docs]
Ancestors vfmTestDefs2165
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2165_0.nsv", "result2165_1.nsv", "result2165_2.nsv", "result2165_3.nsv", "result2165_4.nsv", "result2165_5.nsv", "result2165_6.nsv", "result2165_7.nsv", "result2165_8.nsv", "result2165_9.nsv", "result2165_10.nsv", "result2165_11.nsv", "result2165_12.nsv", "result2165_13.nsv", "result2165_14.nsv", "result2165_15.nsv", "result2165_16.nsv", "result2165_17.nsv", "result2165_18.nsv", "result2165_19.nsv", "result2165_20.nsv", "result2165_21.nsv", "result2165_22.nsv", "result2165_23.nsv"];
val thyn = "vfmTestDefs2165";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
