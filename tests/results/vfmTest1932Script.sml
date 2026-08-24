Theory vfmTest1932[no_sig_docs]
Ancestors vfmTestDefs1932
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1932_0.nsv", "result1932_1.nsv", "result1932_2.nsv", "result1932_3.nsv", "result1932_4.nsv", "result1932_5.nsv", "result1932_6.nsv", "result1932_7.nsv"];
val thyn = "vfmTestDefs1932";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
