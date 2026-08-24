Theory vfmTest2597[no_sig_docs]
Ancestors vfmTestDefs2597
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2597_0.nsv", "result2597_1.nsv", "result2597_2.nsv", "result2597_3.nsv"];
val thyn = "vfmTestDefs2597";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
