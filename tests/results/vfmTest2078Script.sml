Theory vfmTest2078[no_sig_docs]
Ancestors vfmTestDefs2078
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2078_0.nsv", "result2078_1.nsv", "result2078_2.nsv", "result2078_3.nsv", "result2078_4.nsv", "result2078_5.nsv", "result2078_6.nsv", "result2078_7.nsv", "result2078_8.nsv", "result2078_9.nsv", "result2078_10.nsv", "result2078_11.nsv", "result2078_12.nsv", "result2078_13.nsv", "result2078_14.nsv", "result2078_15.nsv"];
val thyn = "vfmTestDefs2078";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
