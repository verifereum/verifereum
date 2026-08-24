Theory vfmTest1994[no_sig_docs]
Ancestors vfmTestDefs1994
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1994_0.nsv", "result1994_1.nsv", "result1994_2.nsv", "result1994_3.nsv", "result1994_4.nsv", "result1994_5.nsv", "result1994_6.nsv", "result1994_7.nsv", "result1994_8.nsv", "result1994_9.nsv", "result1994_10.nsv", "result1994_11.nsv", "result1994_12.nsv", "result1994_13.nsv", "result1994_14.nsv", "result1994_15.nsv"];
val thyn = "vfmTestDefs1994";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
