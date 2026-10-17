Theory vfmTest2224[no_sig_docs]
Ancestors vfmTestDefs2224
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2224_0.nsv", "result2224_1.nsv", "result2224_2.nsv", "result2224_3.nsv", "result2224_4.nsv", "result2224_5.nsv", "result2224_6.nsv", "result2224_7.nsv", "result2224_8.nsv", "result2224_9.nsv", "result2224_10.nsv", "result2224_11.nsv", "result2224_12.nsv", "result2224_13.nsv", "result2224_14.nsv", "result2224_15.nsv", "result2224_16.nsv"];
val thyn = "vfmTestDefs2224";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
