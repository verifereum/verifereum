Theory vfmTest2434[no_sig_docs]
Ancestors vfmTestDefs2434
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2434_0.nsv", "result2434_1.nsv", "result2434_2.nsv", "result2434_3.nsv", "result2434_4.nsv", "result2434_5.nsv", "result2434_6.nsv", "result2434_7.nsv"];
val thyn = "vfmTestDefs2434";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
