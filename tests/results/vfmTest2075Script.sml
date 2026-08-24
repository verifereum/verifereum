Theory vfmTest2075[no_sig_docs]
Ancestors vfmTestDefs2075
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2075_0.nsv", "result2075_1.nsv", "result2075_2.nsv", "result2075_3.nsv", "result2075_4.nsv", "result2075_5.nsv", "result2075_6.nsv", "result2075_7.nsv", "result2075_8.nsv", "result2075_9.nsv", "result2075_10.nsv", "result2075_11.nsv", "result2075_12.nsv", "result2075_13.nsv", "result2075_14.nsv", "result2075_15.nsv"];
val thyn = "vfmTestDefs2075";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
