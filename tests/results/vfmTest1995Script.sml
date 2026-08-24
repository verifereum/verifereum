Theory vfmTest1995[no_sig_docs]
Ancestors vfmTestDefs1995
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1995_0.nsv", "result1995_1.nsv", "result1995_2.nsv", "result1995_3.nsv", "result1995_4.nsv", "result1995_5.nsv", "result1995_6.nsv", "result1995_7.nsv", "result1995_8.nsv"];
val thyn = "vfmTestDefs1995";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
