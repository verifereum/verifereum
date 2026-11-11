Theory vfmTest2150[no_sig_docs]
Ancestors vfmTestDefs2150
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2150_0.nsv", "result2150_1.nsv", "result2150_2.nsv", "result2150_3.nsv", "result2150_4.nsv", "result2150_5.nsv", "result2150_6.nsv", "result2150_7.nsv", "result2150_8.nsv", "result2150_9.nsv", "result2150_10.nsv", "result2150_11.nsv", "result2150_12.nsv", "result2150_13.nsv", "result2150_14.nsv", "result2150_15.nsv", "result2150_16.nsv", "result2150_17.nsv", "result2150_18.nsv", "result2150_19.nsv", "result2150_20.nsv", "result2150_21.nsv", "result2150_22.nsv", "result2150_23.nsv"];
val thyn = "vfmTestDefs2150";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
