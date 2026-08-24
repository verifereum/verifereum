Theory vfmTest1988[no_sig_docs]
Ancestors vfmTestDefs1988
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1988_0.nsv", "result1988_1.nsv", "result1988_2.nsv", "result1988_3.nsv", "result1988_4.nsv", "result1988_5.nsv", "result1988_6.nsv", "result1988_7.nsv", "result1988_8.nsv", "result1988_9.nsv", "result1988_10.nsv", "result1988_11.nsv", "result1988_12.nsv", "result1988_13.nsv", "result1988_14.nsv", "result1988_15.nsv", "result1988_16.nsv", "result1988_17.nsv", "result1988_18.nsv", "result1988_19.nsv"];
val thyn = "vfmTestDefs1988";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
