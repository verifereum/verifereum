Theory vfmTest1754[no_sig_docs]
Ancestors vfmTestDefs1754
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1754_0.nsv", "result1754_1.nsv", "result1754_2.nsv", "result1754_3.nsv", "result1754_4.nsv", "result1754_5.nsv", "result1754_6.nsv", "result1754_7.nsv", "result1754_8.nsv", "result1754_9.nsv", "result1754_10.nsv", "result1754_11.nsv", "result1754_12.nsv", "result1754_13.nsv", "result1754_14.nsv", "result1754_15.nsv"];
val thyn = "vfmTestDefs1754";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
