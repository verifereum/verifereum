Theory vfmTest1986[no_sig_docs]
Ancestors vfmTestDefs1986
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1986_0.nsv", "result1986_1.nsv", "result1986_2.nsv", "result1986_3.nsv", "result1986_4.nsv", "result1986_5.nsv", "result1986_6.nsv", "result1986_7.nsv", "result1986_8.nsv", "result1986_9.nsv", "result1986_10.nsv", "result1986_11.nsv", "result1986_12.nsv", "result1986_13.nsv", "result1986_14.nsv", "result1986_15.nsv", "result1986_16.nsv", "result1986_17.nsv", "result1986_18.nsv", "result1986_19.nsv"];
val thyn = "vfmTestDefs1986";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
