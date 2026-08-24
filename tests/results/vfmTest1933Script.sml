Theory vfmTest1933[no_sig_docs]
Ancestors vfmTestDefs1933
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1933_0.nsv", "result1933_1.nsv", "result1933_2.nsv", "result1933_3.nsv", "result1933_4.nsv", "result1933_5.nsv", "result1933_6.nsv", "result1933_7.nsv"];
val thyn = "vfmTestDefs1933";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
