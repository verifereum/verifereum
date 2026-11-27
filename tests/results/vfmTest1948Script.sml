Theory vfmTest1948[no_sig_docs]
Ancestors vfmTestDefs1948
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1948_0.nsv", "result1948_1.nsv", "result1948_2.nsv", "result1948_3.nsv", "result1948_4.nsv", "result1948_5.nsv", "result1948_6.nsv", "result1948_7.nsv"];
val thyn = "vfmTestDefs1948";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
