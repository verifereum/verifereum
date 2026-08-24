Theory vfmTest1989[no_sig_docs]
Ancestors vfmTestDefs1989
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1989_0.nsv", "result1989_1.nsv", "result1989_2.nsv", "result1989_3.nsv", "result1989_4.nsv", "result1989_5.nsv", "result1989_6.nsv", "result1989_7.nsv", "result1989_8.nsv", "result1989_9.nsv", "result1989_10.nsv", "result1989_11.nsv", "result1989_12.nsv", "result1989_13.nsv", "result1989_14.nsv", "result1989_15.nsv", "result1989_16.nsv", "result1989_17.nsv", "result1989_18.nsv", "result1989_19.nsv"];
val thyn = "vfmTestDefs1989";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
